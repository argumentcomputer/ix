module

public import Ix.Meta
public import Tests.Aiur.Common

public def serdeNatAddComm : IO AiurTestCase := do
  let env ← get_env!
  let natAddCommName := ``Nat.add_comm
  let constList := Lean.collectDependencies natAddCommName env.constants
  let rawEnv ← Ix.CompileM.rsCompileEnvFFI constList
  let ixonEnv := rawEnv.toEnv
  let ixonConsts := ixonEnv.consts.valuesIter
  let (ioBuffer, n) := ixonConsts.fold (init := (default, 0)) fun (ioBuffer, i) c =>
    let (_, bytes) := Ixon.Serialize.put c |>.run default
    (ioBuffer.extend #[.ofNat i] (bytes.data.map .ofUInt8), i + 1)
  pure ⟨`ixon_serde_test, "Ixon serde test", #[.ofNat n], #[], ioBuffer, ioBuffer⟩
