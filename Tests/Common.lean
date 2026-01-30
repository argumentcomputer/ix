/-
  Common test utilities.
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
  input : Array Aiur.G
  expectedOutput : Array Aiur.G
  inputIOBuffer: Aiur.IOBuffer
  expectedIOBuffer: Aiur.IOBuffer

def AiurTestCase.noIO :=
  (AiurTestCase.mk · · · default default)

def commitmentParameters : Aiur.CommitmentParameters := {
  logBlowup := 1
}

def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  numQueries := 100
  commitProofOfWorkBits := 20
  queryProofOfWorkBits := 0
}

def mkAiurTests (toplevelFn : Except Aiur.Global Aiur.Toplevel)
    (cases : List AiurTestCase) : TestSeq :=
  withExceptOk "Toplevel merging succeeds" toplevelFn fun toplevel =>
    withExceptOk "Check and simplification succeed" toplevel.checkAndSimplify fun decls =>
      let bytecodeToplevel := decls.compile
      let aiurSystem := Aiur.AiurSystem.build bytecodeToplevel commitmentParameters
      let runTestCase := fun testCase =>
        let functionName := testCase.functionName
        let funIdx := toplevel.getFuncIdx functionName |>.get!
        let (claim, proof, ioBuffer) := aiurSystem.prove
          friParameters funIdx testCase.input testCase.inputIOBuffer
        let claimTest := test s!"Claim matches for {functionName}"
          (claim == Aiur.buildClaim funIdx testCase.input testCase.expectedOutput)
        let ioTest := test s!"IOBuffer matches for {functionName}"
          (ioBuffer == testCase.expectedIOBuffer)
        let proof := .ofBytes proof.toBytes
        let pvTest := withExceptOk s!"Prove/verify works for {functionName}"
          (aiurSystem.verify friParameters claim proof) fun _ => .done
        claimTest ++ ioTest ++ pvTest
      cases.foldl (init := .done) fun tSeq testCase =>
        tSeq ++ runTestCase testCase
