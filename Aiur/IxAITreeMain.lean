import IxAITree
import Aiur.Library.U32.Hints
import Aiur.Library.U64.Hints

/-! `ixai_tree check` runs `FixedTree::train_tree` on the full configuration with honest hints and
checks the trained model against `IxAICore.train`; `ixai_tree export DIR` writes the execution
package `DIR/train-tree.ixa` (the program compiled with `FixedTree::train_tree` as its only entry,
the initial model and learning rate as arguments, and the hint table of all 600 steps),
`DIR/models.txt` (the parameters after each step, one line per step) and `DIR/batches.txt`
(each batch's 20 inputs of 8 then 20 targets of 11, one line per step). -/

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

/-- The `fx.bound` hint entries of the parameter values `vs`, without repeats. -/
def boundEntries (vs : List Int) : Array (Execution.HintEntry F) :=
  ((dedup vs).map fun v =>
    (⟨.array .field 2, .field (ofInt v), .array .field ((boundWords v).map .field), "fx.bound"⟩ :
      Execution.HintEntry F)).toArray

/-- The two bytes a word is hashed as: `v + 32768`, little-endian. -/
def encBytes (v : Int) : List F :=
  let n := (v + 32768).toNat
  [((n % 256 : Nat) : F), ((n / 256 : Nat) : F)]

def params (m : IxAICore.Model) : List IxAICore.Fx := m.w1.flatten ++ m.b1 ++ m.w2.flatten ++ m.b2

/-- The full configuration's initial model, learning rate, gathered batches and the model after
each step, checked against `IxAICore.train`. -/
def treeRun : IO (IxAICore.Model × IxAICore.Fx × List (List (List IxAICore.Fx × List IxAICore.Fx)) ×
    List IxAICore.Model) := do
  let cfg := fullConfig
  let s := IxAICore.Triage.spec
  let examples := (cfg.data s).map s.example
  let batches := IxAICore.gather examples cfg.schedule (s.example default)
  let lr : IxAICore.Fx := ⟨cfg.lrRaw⟩
  let m0 := cfg.init s
  unless batches.length == 600 && batches.all (fun b => b.length == 20 &&
      b.all fun (x, t) => x.length == 8 && t.length == 11 &&
        (x ++ t).all fun v => -32768 ≤ v.raw && v.raw < 32768) do
    throw (IO.userError "FixedTree::train_tree takes 600 batches of 20 examples within 16 bits")
  let mut m := m0
  let mut models : Array IxAICore.Model := #[]
  for b in batches do
    m := m.step lr b
    models := models.push m
  unless decide (m = IxAICore.train s cfg) do throw (IO.userError "folded steps differ from IxAICore.train")
  return (m0, lr, batches, models.toList)

def rowsOf (rows : List (List IxAICore.Fx)) : List (List F) :=
  rows.map fun r => r.flatMap fun v => encBytes v.raw

/-- The honest hints of `train_tree`: the batches and the byte encoding, then `hints` and the
word libraries' channels used by BLAKE3. -/
def treeHints (batches : List (List (List IxAICore.Fx × List IxAICore.Fx))) : HintDispatcher F :=
  fun channel key =>
    let rows := fun (sel : List IxAICore.Fx × List IxAICore.Fx → List IxAICore.Fx) (i : F) =>
      (rowsOf ((batches.getD i.val []).map sel)).map fun r => (Value.tuple (r.map .field) : Value F Empty)
    match channel, key with
    | "fx.enc", .field v => .ok (.tuple ((encBytes (toInt v)).map .field))
    | "fx.xs", .field i => .ok (.tuple (rows (·.1) i))
    | "fx.ts", .field i => .ok (.tuple (rows (·.2) i))
    | c, k => Library.U32.hints ZMod.val (Library.U64.hints ZMod.val hints) c k

def treeArgs (m : IxAICore.Model) (lr : IxAICore.Fx) : List (SourceValue F) :=
  [mat m.w1, vec m.b1, mat m.w2, vec m.b2, fx lr]

def hex (bytes : List Nat) : String :=
  String.join (bytes.map fun b => String.mk [Nat.digitChar (b / 16), Nat.digitChar (b % 16)])

def checkTree : IO Unit := do
  let (m0, lr, batches, models) ← treeRun
  let prepared ← get <| Modules.prepare (treeSource.toField F) ["FixedTree::train_tree"]
  let honest := prepared.environment.source.checkedHints (treeHints batches)
  let t0 ← IO.monoMsNow
  let (actual, _) ← get <| prepared.run "FixedTree::train_tree" (treeArgs m0 lr) (fuel := 100000000000) (hints := honest)
  let .tuple [.tuple root, w1, b1, w2, b2] := actual
    | throw (IO.userError "unexpected train_tree output shape")
  unless (Value.tuple [w1, b1, w2, b2] : SourceValue F) == modelValue (models.getLast!) do
    throw (IO.userError "Aiur train_tree differs from IxAICore.train")
  let rootBytes := root.filterMap fun | .field b => some b.val | _ => none
  IO.println s!"Aiur train_tree equals IxAICore.train over {batches.length} steps ({(← IO.monoMsNow) - t0} ms semantic evaluation); root {hex rootBytes}"

def exportTree (dir : String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let (m0, lr, batches, models) ← treeRun
  let mut shr : Array Int := #[]
  let mut sign : Array Int := #[]
  let mut bound : Array Int := #[]
  let mut m := m0
  for (b, next) in batches.zip models do
    let (k1, k2) := stepHintKeys m b lr
    shr := shr ++ k1.toArray
    sign := sign ++ k2.toArray
    bound := bound ++ ((params next).map (·.raw)).toArray
    m := next
  let boundKeys := dedup bound.toList
  let enc : Array (Execution.HintEntry F) := (boundKeys.map fun v =>
    (⟨.array .field 2, .field (ofInt v), .array .field ((encBytes v).map .field), "fx.enc"⟩ :
      Execution.HintEntry F)).toArray
  let rowEntries := fun (channel : String) (width : Nat)
      (sel : List IxAICore.Fx × List IxAICore.Fx → List IxAICore.Fx) =>
    ((batches.zip (List.range batches.length)).map fun (b, i) =>
      (⟨.array (.array .field width) 20, .field (i : F),
        .array (.array .field width) ((rowsOf (b.map sel)).map fun r => .array .field (r.map .field)),
        channel⟩ : Execution.HintEntry F)).toArray
  let entriesTable := hintTable (dedup shr.toList, dedup sign.toList) ++ boundEntries boundKeys ++
    enc ++ rowEntries "fx.xs" 16 (·.1) ++ rowEntries "fx.ts" 22 (·.2)
  IO.println s!"hint entries: {entriesTable.size} ({(← IO.monoMsNow) - t0} ms)"
  let treeOnly ← get <| Modules.prepare (treeSource.toField F) ["FixedTree::train_tree"]
  let execution ← get treeOnly.exportExecution
  let compiled ← get (treeOnly.compileOptimized {})
  let (execution, trace) ← get (Trace.exportPlan p ZMod.val compiled.circuit.inlined.program
    compiled.circuit.artifact execution)
  IO.println s!"compiled the tree circuit in {(← IO.monoMsNow) - t0} ms, {compiled.circuit.system.chips.length} chips"
  let table ← get (execution.prepareHints entriesTable)
  let encF := fun (x : IxAICore.Fx) => (ofInt x.raw).val
  let args := (params m0 ++ [lr]).map encF
  IO.FS.createDirAll dir
  Artifact.write s!"{dir}/train-tree.ixa" (← get (Artifact.execution execution p ZMod.val (some trace) args [] table))
  let line := fun (vs : List IxAICore.Fx) => " ".intercalate (vs.map (toString ·.raw))
  IO.FS.writeFile s!"{dir}/models.txt" ("\n".intercalate (models.map (line ∘ params)) ++ "\n")
  IO.FS.writeFile s!"{dir}/batches.txt" ("\n".intercalate (batches.map fun b =>
    line ((b.map (·.1)).flatten ++ (b.map (·.2)).flatten)) ++ "\n")
  IO.println s!"exported FixedTree::train_tree ({args.length} argument words, {table.size} hint entries) to {dir} in {(← IO.monoMsNow) - t0} ms"

end IxAIAiur

def main (args : List String) : IO Unit :=
  match args with
  | ["check"] => IxAIAiur.checkTree
  | ["export", dir] => IxAIAiur.exportTree dir
  | _ => IO.eprintln "usage: ixai_tree check | export DIR"
