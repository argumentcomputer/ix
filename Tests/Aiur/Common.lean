module

public import LSpec
public import Tests.Gen.Basic
public import Ix.Unsigned
public import Ix.Aiur.Goldilocks
public import Ix.Aiur.Protocol
public import Ix.Aiur.Simple
public import Ix.Aiur.Compile

public section

open LSpec SlimCheck Gen

structure AiurTestCase where
  functionName : Lean.Name
  label : String
  input : Array Aiur.G
  expectedOutput : Array Aiur.G
  inputIOBuffer: Aiur.IOBuffer
  expectedIOBuffer: Aiur.IOBuffer

def AiurTestCase.noIO (name : Lean.Name) :=
  (AiurTestCase.mk name (toString name) · · default default)

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
  toplevel : Aiur.Toplevel
  bytecode : Aiur.Bytecode.Toplevel
  aiurSystem : Aiur.AiurSystem

def AiurTestEnv.build (toplevelFn : Except Aiur.Global Aiur.Toplevel) :
    Except String AiurTestEnv := do
  let toplevel ← toplevelFn.mapError toString
  let decls ← toplevel.checkAndSimplify.mapError toString
  let bytecode ← decls.compile
  let aiurSystem := Aiur.AiurSystem.build bytecode commitmentParameters
  return ⟨toplevel, bytecode, aiurSystem⟩

def AiurTestEnv.runTestCase (env : AiurTestEnv) (testCase : AiurTestCase) : TestSeq :=
  let label := testCase.label
  let funIdx := env.toplevel.getFuncIdx testCase.functionName |>.get!
  let (execOutput, execIOBuffer) := env.bytecode.execute
    funIdx testCase.input testCase.inputIOBuffer
  let execOutputTest := test s!"Execute output matches for {label}"
    (execOutput == testCase.expectedOutput)
  let execIOTest := test s!"Execute IOBuffer matches for {label}"
    (execIOBuffer == testCase.expectedIOBuffer)
  let (claim, proof, ioBuffer) := env.aiurSystem.prove
    friParameters funIdx testCase.input testCase.inputIOBuffer
  let claimTest := test s!"Claim matches for {label}"
    (claim == Aiur.buildClaim funIdx testCase.input testCase.expectedOutput)
  let ioTest := test s!"IOBuffer matches for {label}"
    (ioBuffer == testCase.expectedIOBuffer)
  let proof := .ofBytes proof.toBytes
  let pvTest := withExceptOk s!"Prove/verify works for {label}"
    (env.aiurSystem.verify friParameters claim proof) fun _ => .done
  execOutputTest ++ execIOTest ++ claimTest ++ ioTest ++ pvTest

def mkAiurTests (toplevelFn : Except Aiur.Global Aiur.Toplevel)
    (cases : List AiurTestCase) : TestSeq :=
  withExceptOk "Toplevel merging succeeds" toplevelFn fun toplevel =>
    withExceptOk "Check and simplification succeed" toplevel.checkAndSimplify fun decls =>
      withExceptOk "Compilation succeeds" decls.compile fun bytecode =>
        let aiurSystem := Aiur.AiurSystem.build bytecode commitmentParameters
        let env : AiurTestEnv := ⟨toplevel, bytecode, aiurSystem⟩
        cases.foldl (init := .done) fun tSeq testCase =>
          tSeq ++ env.runTestCase testCase

end
