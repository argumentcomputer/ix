module
public import Ix.Aggr
public import LegacyAiur.Compiler
public import LegacyIxVM
public import LegacyIxVM.Toplevel

/-! Compilation and system construction shared by aggregation commands. -/

public section
namespace Aggr

private def compileToplevel (label : String)
    (source : Except LegacyAiur.Global LegacyAiur.Source.Toplevel)
    (groups : Array (String × Array String)) :
    IO (Except String LegacyAiur.CompiledToplevel) := do
  match source with
  | .error e => return Except.error s!"{label} toplevel merge failed: {e}"
  | .ok top => match top.compileWithGroups groups with
    | .error e => return Except.error s!"{label} compilation failed: {e}"
    | .ok compiled => return Except.ok compiled

structure CompiledBackend where
  compiled : LegacyAiur.CompiledToplevel
  system : LegacyAiur.AiurSystem
  vk : ByteArray

/-- Compile a Lean-authored LegacyAiur program, then perform the Rust-side system
construction and verifying-key serialization in the same worker. Keeping this
pipeline together lets the independent LegacyIxVM and recursion backends build in
parallel instead of serializing their Rust setup on the controller thread. -/
def compileBackend (label : String)
    (source : Unit → Except LegacyAiur.Global LegacyAiur.Source.Toplevel)
    (groups : Array (String × Array String))
    (commitment : LegacyAiur.CommitmentParameters) (fri : LegacyAiur.FriParameters) :
    IO (Except String CompiledBackend) := do
  let source ← IO.lazyPure source
  let compiled ← match ← compileToplevel label source groups with
    | .error e => return .error e
    | .ok compiled => pure compiled
  let system := LegacyAiur.AiurSystem.build compiled.bytecode commitment fri
  let vk := system.vkBytes
  return .ok { compiled, system, vk }


structure VerificationBackend where
  system : LegacyAiur.AiurSystem
  aggrIdx : LegacyAiur.Bytecode.FunIdx
  allowed : ByteArray

/-- Build the two deterministic systems whose identities are committed by an
aggregate root: the LegacyIxVM vk and the single-entrypoint recursion vk. -/
def buildVerificationBackend
    (recursionParameters : Aggr.RecursionParameters) :
    IO (Except String VerificationBackend) := do
  let ixvm ← match ← compileBackend "LegacyIxVM" (fun _ => LegacyIxVM.ixVM)
      LegacyIxVM.functionGroups LegacyAiur.defaultCommitmentParameters LegacyAiur.defaultFriParameters with
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
