import Ix.IxVM
import Tests.Ix.IxVM
import Tests.Aiur.Common

def buildIxVMEnv : IO AiurTestEnv := do
  match AiurTestEnv.build IxVM.ixVM with
  | .error e => throw <| IO.userError s!"Aiur setup failed: {e}"
  | .ok env => pure env

def mkCase (caseName : String) (leanEnv : Lean.Environment) : IO AiurTestCase := do
  match caseName with
  | "kernel_unit_tests" => pure <| AiurTestCase.exec `kernel_unit_tests
  | "serde" => serdeNatAddComm leanEnv
  | "Nat.add_comm" => kernelCheck ``Nat.add_comm leanEnv
  | "Nat.sub_le_of_le_add" => kernelCheck ``Nat.sub_le_of_le_add leanEnv
  | "String.Internal.append" => kernelCheck ``String.Internal.append leanEnv
  | "extractMainModule" =>
      kernelCheck (`_private.Init.Prelude |>.mkNum 0 |>.mkStr "Lean.extractMainModule._unsafe_rec") leanEnv
  | other => throw <| IO.userError s!"unknown case: {other}"

def runCase (env : AiurTestEnv) (tc : AiurTestCase) : IO UInt32 := do
  IO.println s!"running {tc.label}"
  let some funIdx := env.compiled.getFuncIdx tc.functionName
    | throw <| IO.userError s!"missing function: {tc.functionName}"
  let (execOutput, execIOBuffer, _queryCounts) :=
    env.compiled.bytecode.execute funIdx tc.input tc.inputIOBuffer
  IO.println s!"output ok: {execOutput == tc.expectedOutput}"
  IO.println s!"io ok: {execIOBuffer == tc.expectedIOBuffer}"
  pure <| if execOutput == tc.expectedOutput && execIOBuffer == tc.expectedIOBuffer then 0 else 1

def main (args : List String) : IO UInt32 := do
  let caseName := args.headD "kernel_unit_tests"
  let leanEnv ← get_env!
  let aiurEnv ← buildIxVMEnv
  let tc ← mkCase caseName leanEnv
  runCase aiurEnv tc
