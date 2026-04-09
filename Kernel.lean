import Ix.Meta
import Ix.Aiur.Protocol
import Ix.Aiur.Statistics
import Ix.Aiur.Interpret
import Ix.IxVM
import Tests.Ix.IxVM
import Tests.Aiur.Common

def parseName (arg : String) : Lean.Name :=
  arg.splitOn "." |>.foldl (init := .anonymous)
    fun acc s => match s.toNat? with
      | some n => Lean.Name.mkNum acc n
      | none   => Lean.Name.mkStr acc s

def main (args : List String) : IO UInt32 := do
  let env ← get_env!
  let dbg := args.contains "--dbg"
  let args := args.filter (· != "--dbg")
  let toplevel ← match IxVM.ixVM with
    | .error e => IO.eprintln s!"Toplevel merging failed: {e}"; return 1
    | .ok t => pure t
  let run ← if dbg then
      let decls ← match toplevel.mkDecls with
        | .error e => IO.eprintln s!"mkDecls failed: {e}"; return 1
        | .ok d => pure d
      pure (interpCheck decls · env)
    else
      let compiled ← match toplevel.compile with
        | .error e => IO.eprintln s!"Compilation failed: {e}"; return 1
        | .ok c => pure c
      pure (check compiled · env)
  if args.isEmpty then
    for (name, _) in env.constants do
      let res ← run name
      if res ≠ 0 then return res
  else
    for arg in args do
      let name := parseName arg
      if !env.constants.contains name then
        IO.eprintln s!"{name} not found"
        return 1
      let res ← run name
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
    if output != testCase.expectedOutput then
      IO.eprintln s!"{name}: output mismatch"
      return 1
    if ioBuffer != testCase.expectedIOBuffer then
      IO.eprintln s!"{name}: IOBuffer mismatch"
      return 1
    let stats := Aiur.computeStats compiled queryCounts
    Aiur.printStats stats
    pure 0
  interpCheck decls name env : IO UInt32 := do
    IO.println s!"Interpreting {name}"
    (← IO.getStdout).flush
    let testCase ← kernelCheck name env
    let funcName := Aiur.Global.mk testCase.functionName
    let inputs := testCase.input.toList.map Aiur.Value.field
    match Aiur.runFunction decls funcName inputs testCase.inputIOBuffer with
    | .error e =>
      IO.eprintln s!"{name}: interpreter error:\n{e}"
      return 1
    | .ok (output, _state) =>
      IO.println s!"{name}: {output}"
      pure 0
