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
  let debugFast := args.contains "--debug-fast"
  let args := args.filter fun a => a != "--dbg" && a != "--debug-fast"
  let toplevel ← match IxVM.ixVM with
    | .error e => IO.eprintln s!"Toplevel merging failed: {e}"; return 1
    | .ok t => pure t
  let run ← if dbg then
      let decls ← match toplevel.mkDecls with
        | .error e => IO.eprintln s!"mkDecls failed: {e}"; return 1
        | .ok d => pure d
      pure (interpCheck decls debugFast · env)
    else
      let compiled ← match toplevel.compile with
        | .error e => IO.eprintln s!"Compilation failed: {e}"; return 1
        | .ok c => pure c
      pure (check compiled debugFast · env)
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
  -- Build the test case for `name`. `debugFast = false` → claim path
  -- (full transitive typecheck); `debugFast = true` → `dbg_check_const`
  -- (subject only, trust deps).
  mkTestCase debugFast name env : IO AiurTestCase := do
    if debugFast then
      let ixonEnv ← IxVM.ClaimHarness.loadIxonEnv name env
      let target ← IxVM.ClaimHarness.lookupAddr ixonEnv name
      let witness := IxVM.ClaimHarness.buildDbgCheckConst ixonEnv target
      pure { functionName := witness.funcName
             label := s!"Kernel check {name}"
             input := witness.input, inputIOBuffer := witness.inputIOBuffer
             expectedIOBuffer := witness.inputIOBuffer
             interpret := false, executionOnly := true }
    else
      kernelCheck name env
  check compiled debugFast name env : IO UInt32 := do
    IO.println s!"Typechecking {name}"
    (← IO.getStdout).flush
    let testCase ← mkTestCase debugFast name env
    let funIdx := compiled.getFuncIdx testCase.functionName |>.get!
    match compiled.bytecode.execute funIdx testCase.input testCase.inputIOBuffer with
    | .error e =>
      IO.eprintln s!"{name}: Aiur execution error: {e}"
      return 1
    | .ok (output, ioBuffer, queryCounts) =>
      if output != testCase.expectedOutput then
        IO.eprintln s!"{name}: output mismatch"
        return 1
      if ioBuffer != testCase.expectedIOBuffer then
        IO.eprintln s!"{name}: IOBuffer mismatch"
        return 1
      let stats := Aiur.computeStats compiled queryCounts
      Aiur.printStats stats
      pure 0
  interpCheck decls debugFast name env : IO UInt32 := do
    IO.println s!"Interpreting {name}"
    (← IO.getStdout).flush
    let testCase ← mkTestCase debugFast name env
    let funcName := Aiur.Global.mk testCase.functionName
    -- Get function's input types to properly unflatten the input array
    let inputTypes ← match decls.getByKey funcName with
      | some (.function f) => pure $ f.inputs.map (·.2)
      | _ => IO.eprintln s!"{name}: function not found in decls"; return 1
    let inputs := Aiur.unflattenInputs decls testCase.input inputTypes
    match Aiur.runFunction decls funcName inputs testCase.inputIOBuffer with
    | (.error e, s) =>
      IO.eprintln s!"{name}: interpreter error:\n{e.ppDeref s.store 1 10}"
      return 1
    | (.ok output, _) =>
      IO.println s!"{name}: {output}"
      pure 0
