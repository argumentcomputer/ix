/-
  Common Aiur test utilities.
  Basic type generators have been moved to Tests/Gen/Basic.lean.
-/

import LSpec
import Tests.Gen.Basic
import Ix.Unsigned
import Ix.Aiur.Goldilocks
import Ix.Aiur.Protocol
import Ix.Aiur.Simple
import Ix.Aiur.Compile

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
}

def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  numQueries := 100
  commitProofOfWorkBits := 20
  queryProofOfWorkBits := 0
}

structure AiurTestEnv where
  toplevel : Aiur.Toplevel
  aiurSystem : Aiur.AiurSystem

def AiurTestEnv.build (toplevelFn : Except Aiur.Global Aiur.Toplevel) :
    Except String AiurTestEnv := do
  let toplevel ← toplevelFn.mapError toString
  let decls ← toplevel.checkAndSimplify.mapError toString
  let bytecodeToplevel := decls.compile
  let aiurSystem := Aiur.AiurSystem.build bytecodeToplevel commitmentParameters
  return ⟨toplevel, aiurSystem⟩

def AiurTestEnv.runTestCase (env : AiurTestEnv) (testCase : AiurTestCase) : TestSeq :=
  let label := testCase.label
  let funIdx := env.toplevel.getFuncIdx testCase.functionName |>.get!
  let (claim, proof, ioBuffer) := env.aiurSystem.prove
    friParameters funIdx testCase.input testCase.inputIOBuffer
  let claimTest := test s!"Claim matches for {label}"
    (claim == Aiur.buildClaim funIdx testCase.input testCase.expectedOutput)
  let ioTest := test s!"IOBuffer matches for {label}"
    (ioBuffer == testCase.expectedIOBuffer)
  let proof := .ofBytes proof.toBytes
  let pvTest := withExceptOk s!"Prove/verify works for {label}"
    (env.aiurSystem.verify friParameters claim proof) fun _ => .done
  claimTest ++ ioTest ++ pvTest

def mkAiurTests (toplevelFn : Except Aiur.Global Aiur.Toplevel)
    (cases : List AiurTestCase) : TestSeq :=
  withExceptOk "Toplevel merging succeeds" toplevelFn fun toplevel =>
    withExceptOk "Check and simplification succeed" toplevel.checkAndSimplify fun decls =>
      let bytecodeToplevel := decls.compile
      let aiurSystem := Aiur.AiurSystem.build bytecodeToplevel commitmentParameters
      let env : AiurTestEnv := ⟨toplevel, aiurSystem⟩
      cases.foldl (init := .done) fun tSeq testCase =>
        tSeq ++ env.runTestCase testCase
