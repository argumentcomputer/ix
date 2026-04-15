module

public import LSpec
public import Tests.Gen.Basic
public import Ix.Unsigned
public import Ix.Aiur.Goldilocks
public import Ix.Aiur.Protocol
public import Ix.Aiur.Compiler
public import Ix.Aiur.Interpret

public section

open LSpec SlimCheck Gen

structure AiurTestCase where
  functionName : Lean.Name
  label : String := toString functionName
  input : Array Aiur.G := #[]
  expectedOutput : Array Aiur.G := #[]
  inputIOBuffer : Aiur.IOBuffer := default
  expectedIOBuffer : Aiur.IOBuffer := default
  interpret : Bool := true
  executionOnly : Bool := false

def AiurTestCase.noIO (functionName : Lean.Name)
    (input expectedOutput : Array Aiur.G) : AiurTestCase :=
  { functionName, input, expectedOutput }

def AiurTestCase.exec (functionName : Lean.Name)
    (input : Array Aiur.G := #[]) (expectedOutput : Array Aiur.G := #[]) : AiurTestCase :=
  { functionName, input, expectedOutput, interpret := false, executionOnly := true }

def commitmentParameters : Aiur.CommitmentParameters := {
  logBlowup := 1
  capHeight := 0
}

def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 100
  commitProofOfWorkBits := 20
  queryProofOfWorkBits := 0
}

structure AiurTestEnv where
  compiled : Aiur.CompiledToplevel
  decls : Aiur.Source.Decls
  aiurSystem : Aiur.AiurSystem

def AiurTestEnv.build (toplevelFn : Except Aiur.Global Aiur.Source.Toplevel) :
    Except String AiurTestEnv := do
  let toplevel ← toplevelFn.mapError toString
  let compiled ← toplevel.compile
  let decls ← toplevel.mkDecls.mapError toString
  let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitmentParameters
  return ⟨compiled, decls, aiurSystem⟩

def AiurTestEnv.interpTest (env : AiurTestEnv) (testCase : AiurTestCase)
    (execOutput : Array Aiur.G) (execIOBuffer : Aiur.IOBuffer) : TestSeq :=
  let label := testCase.label
  let funcName := Aiur.Global.mk testCase.functionName
  let inputTypes := match env.decls.getByKey funcName with
    | some (.function f) => f.inputs.map (·.2)
    | _ => []
  let inputs := Aiur.unflattenInputs env.decls testCase.input inputTypes
  let funcIdx g := env.compiled.getFuncIdx g.toName
  match Aiur.runFunction env.decls funcName inputs testCase.inputIOBuffer with
  | .error e =>
    test s!"Interpret succeeds for {label}: {e}" false
  | .ok (output, state) =>
    let flat := Aiur.flattenValue env.decls funcIdx output
    let interpOutputTest := test s!"Interpret output matches for {label}"
      (flat == execOutput)
    let interpIOTest := test s!"Interpret IOBuffer matches for {label}"
      (state.ioBuffer == execIOBuffer)
    interpOutputTest ++ interpIOTest

def AiurTestEnv.runTestCase (env : AiurTestEnv) (testCase : AiurTestCase) : TestSeq :=
  let label := testCase.label
  let funIdx := env.compiled.getFuncIdx testCase.functionName |>.get!
  let (execOutput, execIOBuffer, _queryCounts) := env.compiled.bytecode.execute
    funIdx testCase.input testCase.inputIOBuffer
  let execOutputTest := test s!"Execute output matches for {label}"
    (execOutput == testCase.expectedOutput)
  let execIOTest := test s!"Execute IOBuffer matches for {label}"
    (execIOBuffer == testCase.expectedIOBuffer)
  let execTest := execOutputTest ++ execIOTest
  let interpTest :=
    if testCase.interpret then env.interpTest testCase execOutput execIOBuffer
    else .done
  if testCase.executionOnly then execTest ++ interpTest
  else
    let (claim, proof, ioBuffer) := env.aiurSystem.prove
      friParameters funIdx testCase.input testCase.inputIOBuffer
    let claimTest := test s!"Claim matches for {label}"
      (claim == Aiur.buildClaim funIdx testCase.input testCase.expectedOutput)
    let ioTest := test s!"IOBuffer matches for {label}"
      (ioBuffer == testCase.expectedIOBuffer)
    let proof := .ofBytes proof.toBytes
    let pvTest := withExceptOk s!"Prove/verify works for {label}"
      (env.aiurSystem.verify friParameters claim proof) fun _ => .done
    execTest ++ interpTest ++ claimTest ++ ioTest ++ pvTest

def mkAiurTests (toplevelFn : Except Aiur.Global Aiur.Source.Toplevel)
    (cases : List AiurTestCase) : TestSeq :=
  withExceptOk "Toplevel merging succeeds" toplevelFn fun toplevel =>
    withExceptOk "Compilation succeeds" toplevel.compile fun compiled =>
      withExceptOk "mkDecls succeeds" (toplevel.mkDecls.mapError toString) fun decls =>
        let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitmentParameters
        let env : AiurTestEnv := ⟨compiled, decls, aiurSystem⟩
        cases.foldl (init := .done) fun tSeq testCase =>
          tSeq ++ env.runTestCase testCase

end
