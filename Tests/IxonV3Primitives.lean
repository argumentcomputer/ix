import Tests.Ix.Kernel.BuildPrimitives

open Tests.Ix.Kernel.BuildPrimitives

def main : IO Unit := do
  let leanEnv ← get_env!
  let needed := collectDeps leanEnv (kernelPrimitives.map parseNameToLean)
  let constants := leanEnv.constants.toList.filter fun (name, _) => needed.contains name
  IO.println s!"Compiling {constants.length} primitive dependency declarations"
  let raw ← Ix.CompileM.rsCompileEnvFFI constants
  let env := raw.toEnv
  let mut text := "# Ixon v3 canonical primitive addresses\n"
  for name in kernelPrimitives do
    let some named := env.named[parseIxName name]?
      | throw <| IO.userError s!"missing primitive {name}"
    text := text ++ s!"{name}\t{named.addr}\n"
  IO.FS.writeFile "/tmp/ixon-v3-primitives.tsv" text
  let bytes ← match Ixon.serEnv env with
    | .ok bytes => pure bytes
    | .error error => throw <| IO.userError error
  IO.FS.writeBinFile "/tmp/ixon-v3-primitives.ixe" bytes
  IO.println s!"Exported {kernelPrimitives.size} primitive addresses and {env.consts.size} constants"
