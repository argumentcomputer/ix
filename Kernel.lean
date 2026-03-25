import Ix.Meta
import Ix.Aiur.Protocol
import Ix.IxVM
import Tests.Aiur.Common

def kernelCheck (name : Lean.Name) (consts : Lean.ConstMap) : IO AiurTestCase := do
  let constList := Lean.collectDependencies name consts
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

  pure { functionName := `kernel_check_test, label := s!"Kernel check {name}"
         input := targetAddrBytes, inputIOBuffer := ioBuffer, expectedIOBuffer := ioBuffer,
         executionOnly := true }

def main (args : List String) : IO UInt32 := do
  let env ← get_env!
  let consts := env.constants
  if args.isEmpty then
    for (name, _) in consts do
      let res ← check name consts
      if res ≠ 0 then return res
  else
    for arg in args do
      let name := arg.splitOn "." |>.foldl (init := .anonymous)
        fun acc s => match s.toNat? with
          | some n => Lean.Name.mkNum acc n
          | none   => Lean.Name.mkStr acc s
      if !consts.contains name then
        IO.eprintln s!"{name} not found"
        return 1
      let res ← check name consts
      if res ≠ 0 then return res
  pure 0
where
  check name env : IO UInt32 := do
    IO.println s!"Typechecking {name}"
    (← IO.getStdout).flush
    let testCase ← kernelCheck name env
    let res ← LSpec.lspecIO (.ofList [(name.toString, [mkAiurTests IxVM.ixVM [testCase]])]) []
    if res ≠ 0 then
      IO.eprintln s!"{name} failed"
    pure res
