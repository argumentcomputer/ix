import Ix.Meta
import Ix.Aiur.Protocol
import Ix.IxVM
import Tests.Ix.IxVM
import Tests.Aiur.Common

def main (args : List String) : IO UInt32 := do
  let env ← get_env!
  if args.isEmpty then
    for (name, _) in env.constants do
      let res ← check name env
      if res ≠ 0 then return res
  else
    for arg in args do
      let name := arg.splitOn "." |>.foldl (init := .anonymous)
        fun acc s => match s.toNat? with
          | some n => Lean.Name.mkNum acc n
          | none   => Lean.Name.mkStr acc s
      if !env.constants.contains name then
        IO.eprintln s!"{name} not found"
        return 1
      let res ← check name env
      if res ≠ 0 then return res
  pure 0
where
  check name env : IO UInt32 := do
    IO.println s!"Typechecking {name}"
    (← IO.getStdout).flush
    let testCase ← kernelCheck name env
    let res ← LSpec.lspecIO (.ofList [(name.toString, [mkAiurTests IxVM.ixVM [testCase]])]) []
    if res ≠ 0 then
      IO.eprintln s!"{name} failed"
    pure res
