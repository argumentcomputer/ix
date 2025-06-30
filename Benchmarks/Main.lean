import Ix.Benchmark.Bench
import Ix.Benchmark.Common
import Ix.Aiur.Bytecode
import Ix.Aiur.Simple
import Ix.Aiur.Execute
import Ix.Aiur.Witness
import Ix.Aiur.Meta
import Ix.Archon.Protocol

def topLevel := ⟦ fn id(n: u64) -> u64 { n } ⟧

structure TestCase where
  functionName : Lean.Name
  input : Array UInt64
  expectedOutput : Array UInt64

def testCase : TestCase := ⟨ `id, #[42], #[42] ⟩

def compile (top : Aiur.Toplevel) : Aiur.Bytecode.Toplevel :=
  let typedDecls := Aiur.checkAndSimplifyToplevel top
  match typedDecls with
  | .ok a => a.compile
  | .error e => panic! s!"Failed to unwrap Aiur typedDecls: {e}"

def prove (bytecodeTopLevel : Aiur.Bytecode.Toplevel) : Archon.Proof :=
  let (aiurCircuits, funcChannels) := Aiur.Circuit.synthesize bytecodeTopLevel
  let circuitModules := aiurCircuits.circuitModules
  let functionName := testCase.functionName
  let input := testCase.input
  let funcIdx := topLevel.getFuncIdx functionName |>.get!
  let record := bytecodeTopLevel.execute funcIdx input
  let output := record.getFuncResult funcIdx input |>.get!
  assert! output == testCase.expectedOutput
  let traces := bytecodeTopLevel.generateTraces record
  let witness := Aiur.Circuit.populateWitness aiurCircuits traces bytecodeTopLevel.gadgets
  let funcChannel := funcChannels[funcIdx]!
  let boundaries := Aiur.Circuit.mkBoundaries testCase.input output funcChannel
  assert! Archon.validateWitness circuitModules boundaries witness |>.isOk
  let (logInvRate, securityBits) := (1, 100)
  let proof := Archon.prove circuitModules boundaries logInvRate securityBits witness
  assert! Archon.verify circuitModules boundaries logInvRate securityBits proof |>.isOk
  proof

def proveBench :=
  let bytecode := compile topLevel
  (bgroup "Prove E2E" [
    bench "prove id" prove bytecode,
  ] { samplingMode := .flat } )

def main : IO Unit := do
  let _result ← proveBench
