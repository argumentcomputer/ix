module

public import Ix.Meta
public import Tests.Aiur.Common

public def serdeNatAddComm (env : Lean.Environment) : IO AiurTestCase := do
  let natAddCommName := ``Nat.add_comm
  let constList := Lean.collectDependencies natAddCommName env.constants
  let rawEnv ← Ix.CompileM.rsCompileEnvFFI constList
  let ixonEnv := rawEnv.toEnv
  let ixonConsts := ixonEnv.consts.valuesIter
  let (ioBuffer, n) := ixonConsts.fold (init := (default, 0)) fun (ioBuffer, i) c =>
    let (_, bytes) := Ixon.Serialize.put c |>.run default
    (ioBuffer.extend #[.ofNat i] (bytes.data.map .ofUInt8), i + 1)
  pure ⟨`ixon_serde_test, "Ixon serde test", #[.ofNat n], #[], ioBuffer, ioBuffer⟩

public def kernelCheckNatAddComm (env : Lean.Environment) : IO AiurTestCase := do
  let constList := Lean.collectDependencies ``Nat.add_comm env.constants
  let rawEnv ← Ix.CompileM.rsCompileEnvFFI constList
  let ixonEnv := rawEnv.toEnv

  let mut ioBuffer : Aiur.IOBuffer := default

  -- Store ALL constants (including muts blocks) by Blake3 hash
  for (addr, c) in ixonEnv.consts do
    let (_, bytes) := Ixon.Serialize.put c |>.run default
    let key : Array Aiur.G := addr.hash.data.map .ofUInt8
    ioBuffer := ioBuffer.extend key (bytes.data.map .ofUInt8)

  -- Get the blake3 address of Nat.add_comm as the target
  let targetAddr := match ixonEnv.getAddr? (Ix.Name.fromLeanName ``Nat.add_comm) with
    | some addr => addr
    | none => panic! "Nat.add_comm not found in Ixon environment"
  let targetAddrBytes : Array Aiur.G := targetAddr.hash.data.map .ofUInt8

  pure ⟨`kernel_check_test, "Kernel check Nat.add_comm",
    targetAddrBytes, #[], ioBuffer, ioBuffer⟩
