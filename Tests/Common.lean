import LSpec
import Ix.Unsigned
import Ix.Aiur.Goldilocks
import Ix.Aiur.Protocol
import Ix.Aiur.Simple
import Ix.Aiur.Compile

open LSpec SlimCheck Gen

def genUInt8 : Gen UInt8 :=
  UInt8.ofNat <$> choose Nat 0 0xFF

def genUInt32 : Gen UInt32 :=
  UInt32.ofNat <$> choose Nat 0 0xFFFFFFFF

def genUInt64 : Gen UInt64 :=
  UInt64.ofNat <$> choose Nat 0 0xFFFFFFFFFFFFFFFF

def genUSize : Gen USize :=
  .ofNat <$> choose Nat 0 (2^System.Platform.numBits - 1)

def frequency' (default: Gen α) (xs: List (Nat × Gen α)) : Gen α := do
  let n ← choose Nat 0 total
  pick n xs
  where
    total := List.sum (Prod.fst <$> xs)
    pick n xs := match xs with
    | [] => default
    | (k, x) :: xs => if n <= k then x else pick (n - k) xs

def frequency [Inhabited α] (xs: List (Nat × Gen α)) : Gen α :=
  frequency' xs.head!.snd xs

def oneOf' [Inhabited α] (xs: List (Gen α)) : Gen α :=
  frequency (xs.map (fun x => (100, x)))

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
  proofOfWorkBits := 20
}

def mkAiurTests (toplevel : Aiur.Toplevel) (cases : List AiurTestCase) : TestSeq :=
  withExceptOk "Check and simplification works" toplevel.checkAndSimplify fun decls =>
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
