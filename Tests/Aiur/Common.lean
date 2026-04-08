module

public import LSpec
public import Tests.Gen.Basic
public import Ix.Unsigned
public import Ix.Aiur.Goldilocks
public import Ix.Aiur.Protocol
public import Ix.Aiur.Compiler

public section

open LSpec SlimCheck Gen

structure AiurTestCase where
  functionName : Lean.Name
  label : String := toString functionName
  input : Array Aiur.G := #[]
  expectedOutput : Array Aiur.G := #[]
  inputIOBuffer : Aiur.IOBuffer := default
  expectedIOBuffer : Aiur.IOBuffer := default
  executionOnly : Bool := false

def AiurTestCase.noIO (functionName : Lean.Name)
    (input expectedOutput : Array Aiur.G) : AiurTestCase :=
  { functionName, input, expectedOutput }

def AiurTestCase.exec (functionName : Lean.Name)
    (input : Array Aiur.G := #[]) (expectedOutput : Array Aiur.G := #[]) : AiurTestCase :=
  { functionName, input, expectedOutput, executionOnly := true }

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
  aiurSystem : Aiur.AiurSystem

def AiurTestEnv.build (toplevelFn : Except Aiur.Global Aiur.Toplevel) :
    Except String AiurTestEnv := do
  let toplevel ← toplevelFn.mapError toString
  let compiled ← toplevel.compile
  let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitmentParameters
  return ⟨compiled, aiurSystem⟩

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
  if testCase.executionOnly then execTest
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
    execTest ++ claimTest ++ ioTest ++ pvTest

def mkAiurTests (toplevelFn : Except Aiur.Global Aiur.Toplevel)
    (cases : List AiurTestCase) : TestSeq :=
  withExceptOk "Toplevel merging succeeds" toplevelFn fun toplevel =>
    withExceptOk "Compilation succeeds" toplevel.compile fun compiled =>
      let aiurSystem := Aiur.AiurSystem.build compiled.bytecode commitmentParameters
      let env : AiurTestEnv := ⟨compiled, aiurSystem⟩
      cases.foldl (init := .done) fun tSeq testCase =>
        tSeq ++ env.runTestCase testCase

end
