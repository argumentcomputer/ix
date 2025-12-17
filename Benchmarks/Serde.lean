import Ix.Meta
import Ix.CompileFFI
import Ix.IxVM
import Ix.Aiur.Simple
import Ix.Aiur.Compile
import Ix.Aiur.Protocol

def commitmentParameters : Aiur.CommitmentParameters := {
  logBlowup := 1
}

def friParameters : Aiur.FriParameters := {
  logFinalPolyLen := 0
  numQueries := 100
  proofOfWorkBits := 20
}

def main : IO Unit := do
  let .ok ixVM := IxVM.ixVM
    | throw (IO.userError "IxVM merging failed")
  let some funIdx := ixVM.getFuncIdx `serde_bench
    | throw (IO.userError "Aiur function not found")
  let .ok decls := ixVM.checkAndSimplify
    | throw (IO.userError "Simplification failed")
  let aiurSystem := Aiur.AiurSystem.build decls.compile commitmentParameters
  let env ← get_env!
  let consts := Lean.collectDependencies ``Nat.add_comm env.constants
  let (natAddCommAddr, compiledConsts) := Ix.compileConsts ``Nat.add_comm consts
  let toArrayG := (·.data.map .ofUInt8)
  let natAddCommAddr := toArrayG natAddCommAddr.hash
  let ioBuffer := compiledConsts.foldl (init := default) fun ioBuffer (addr, bytes) =>
    ioBuffer.extend (toArrayG addr.hash) (toArrayG bytes)
  let start ← IO.monoMsNow
  let (_, proof, _) := aiurSystem.prove friParameters funIdx natAddCommAddr ioBuffer
  let finish ← IO.monoMsNow
  match aiurSystem.verify friParameters natAddCommAddr proof with
  | .error e => IO.println e
  | .ok _ => println! "{(finish - start).toFloat / 1000.0}s"
