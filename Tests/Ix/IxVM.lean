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

def kernelCheck (name : Lean.Name) (env : Lean.Environment) : IO AiurTestCase := do
  let constList := Lean.collectDependencies name env.constants
  let rawEnv ← Ix.CompileM.rsCompileEnvFFI constList
  let ixonEnv := rawEnv.toEnv

  let mut ioBuffer : Aiur.IOBuffer := default

  -- Store ALL constants (including muts blocks) by Blake3 hash
  for (addr, c) in ixonEnv.consts do
    let (_, bytes) := Ixon.Serialize.put c |>.run default
    let key : Array Aiur.G := addr.hash.data.map .ofUInt8
    ioBuffer := ioBuffer.extend key (bytes.data.map .ofUInt8)

  -- Store each blob:
  -- 1. Raw bytes under prefixed key [1] ++ blake3_hash (for on-demand verified loading)
  -- 2. Empty sentinel under plain blake3_hash (so io_get_info returns len=0, marking as blob)
  for (addr, rawBytes) in ixonEnv.blobs do
    let hashKey : Array Aiur.G := addr.hash.data.map .ofUInt8
    let prefixedKey : Array Aiur.G := #[1] ++ hashKey
    ioBuffer := ioBuffer.extend prefixedKey (rawBytes.data.map fun b => .ofNat b.toNat)
    ioBuffer := ioBuffer.extend hashKey #[]

  -- Get the blake3 address of `name` as the target
  let targetAddr := match ixonEnv.getAddr? (Ix.Name.fromLeanName name) with
    | some addr => addr
    | none => panic! s!"{name} not found in Ixon environment"
  let targetAddrBytes : Array Aiur.G := targetAddr.hash.data.map .ofUInt8

  pure ⟨`kernel_check_test, s!"Kernel check {name}",
    targetAddrBytes, #[], ioBuffer, ioBuffer⟩

public def kernelCheckNatAddComm (env : Lean.Environment) : IO AiurTestCase := do
  kernelCheck ``Nat.add_comm env

public def kernelCheckNatSubLeOfLeAdd (env : Lean.Environment) : IO AiurTestCase := do
  kernelCheck ``Nat.sub_le_of_le_add env
