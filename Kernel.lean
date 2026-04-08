import Ix.Meta
import Ix.Aiur.Protocol
import Ix.Aiur.Statistics
import Ix.IxVM
import Tests.Ix.IxVM
import Tests.Aiur.Common

def main (args : List String) : IO UInt32 := do
  let env ← get_env!
  let toplevel ← match IxVM.ixVM with
    | .error e => IO.eprintln s!"Toplevel merging failed: {e}"; return 1
    | .ok t => pure t
  let compiled ← match toplevel.compile with
    | .error e => IO.eprintln s!"Compilation failed: {e}"; return 1
    | .ok c => pure c
  if args.isEmpty then
    for (name, _) in env.constants do
      let res ← check compiled name env
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
      let res ← check compiled name env
      if res ≠ 0 then return res
  pure 0
where
  check compiled name env : IO UInt32 := do
    IO.println s!"Typechecking {name}"
    (← IO.getStdout).flush
    let testCase ← kernelCheck name env
    let funIdx := compiled.getFuncIdx testCase.functionName |>.get!
    let (output, ioBuffer, queryCounts) :=
      compiled.bytecode.execute funIdx testCase.input testCase.inputIOBuffer
    let outputOk := output == testCase.expectedOutput
    let ioOk := ioBuffer == testCase.expectedIOBuffer
    if !outputOk then
      IO.eprintln s!"{name}: output mismatch"
      return 1
    if !ioOk then
      IO.eprintln s!"{name}: IOBuffer mismatch"
      return 1
    let stats := Aiur.computeStats compiled queryCounts
    Aiur.printStats stats
    pure 0
