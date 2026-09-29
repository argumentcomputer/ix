module
public import Ix.Aggr
public import Ix.Aiur.Compiler
public import Ix.IxVM
public import Ix.IxVM.Toplevel

/-! Compilation and system construction shared by aggregation commands. -/

public section
namespace Aggr

private def compileToplevel (label : String)
    (source : Except Aiur.Global Aiur.Source.Toplevel)
    (groups : Array (String × Array String)) :
    IO (Except String Aiur.CompiledToplevel) := do
  match source with
  | .error e => return Except.error s!"{label} toplevel merge failed: {e}"
  | .ok top => match top.compileWithGroups groups with
    | .error e => return Except.error s!"{label} compilation failed: {e}"
    | .ok compiled => return Except.ok compiled

structure CompiledBackend where
  compiled : Aiur.CompiledToplevel
  system : Aiur.AiurSystem
  vk : ByteArray

/-- Compile a Lean-authored Aiur program, then perform the Rust-side system
construction and verifying-key serialization in the same worker. Keeping this
pipeline together lets the independent IxVM and recursion backends build in
parallel instead of serializing their Rust setup on the controller thread. -/
def compileBackend (label : String)
    (source : Unit → Except Aiur.Global Aiur.Source.Toplevel)
    (groups : Array (String × Array String))
    (commitment : Aiur.CommitmentParameters) (fri : Aiur.FriParameters) :
    IO (Except String CompiledBackend) := do
  let source ← IO.lazyPure source
  let compiled ← match ← compileToplevel label source groups with
    | .error e => return .error e
    | .ok compiled => pure compiled
  let system := Aiur.AiurSystem.build compiled.bytecode commitment fri
  let vk := system.vkBytes
  return .ok { compiled, system, vk }


structure VerificationBackend where
  system : Aiur.AiurSystem
  aggrIdx : Aiur.Bytecode.FunIdx
  allowed : ByteArray

/-- Build the two deterministic systems whose identities are committed by an
aggregate root: the IxVM vk and the single-entrypoint recursion vk. -/
def buildVerificationBackend
    (recursionParameters : Aggr.RecursionParameters) :
    IO (Except String VerificationBackend) := do
  let ixvm ← match ← compileBackend "IxVM" (fun _ => IxVM.ixVM)
      IxVM.functionGroups Aiur.defaultCommitmentParameters Aiur.defaultFriParameters with
    | .error e => return .error e
    | .ok backend => pure backend
  let aggr ← match ← compileBackend "recursion" (fun _ => Aggr.ixAggr)
      Aggr.functionGroups recursionParameters.commitment recursionParameters.fri with
    | .error e => return .error e
    | .ok backend => pure backend
  let verifyIdx := ixvm.compiled.getFuncIdx `verify_claim |>.get!
  let aggrIdx := aggr.compiled.getFuncIdx `ix_aggr |>.get!
  let allowed := Aggr.allowedBlob ixvm.vk verifyIdx aggr.vk aggrIdx
  return .ok {
    system := aggr.system
    aggrIdx
    allowed
  }

end Aggr
end
