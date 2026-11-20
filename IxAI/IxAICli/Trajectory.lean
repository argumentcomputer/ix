import IxAI.TrainClaim
import IxAI.Float
import IxAIVerify.Trajectory

/-!
# `ixai data` and `ixai train`: the reference run of the native training pipeline

The dataset and config an untrusted trainer starts from, and the trajectory the specification
computes, in the text format of `IxAIVerify.Trajectory`. `ixai check` is
`IxAIVerify.Cli.trajectoryCommand`.
-/

namespace IxAICli

open IxAI IxAIVerify

/- Closed subterms such as a reference training run would otherwise become module initializers,
run at every start of `ixai` whatever the command. -/
set_option compiler.extract_closed false

def writeData (path : System.FilePath) (fmt : String) : IO Unit := do
  let s : DataSpec := {}
  let d := s.generate
  let items := d.items.toList.map fun i =>
    s!"item {if i.label then 1 else 0} " ++ joinInts i.features
  IO.FS.writeFile path ("\n".intercalate
    ([configLine defaultConfig, s!"format {fmt}", dataLine s d] ++ items) ++ "\n")
  IO.println s!"wrote {d.items.size} items, root {d.root}, {d.positives} valid formulas"

def writeTrajectory (path : System.FilePath) (fmt : String) : IO UInt32 := do
  let s : DataSpec := {}
  let d := s.generate
  let text := match fmt with
    | "fx" => some (trajectory (α := Fx) fmt defaultConfig s d)
    | "bf16" => some (trajectory (α := BF16) fmt defaultConfig s d)
    | "f32" => some (trajectory (α := F32) fmt defaultConfig s d)
    | _ => none
  match text with
  | some t => IO.FS.writeFile path t; IO.println s!"wrote {defaultConfig.schedule d.items.size |>.length} steps ({fmt})"; return 0
  | none => IO.println s!"unknown format {fmt}"; return 2

end IxAICli
