import Tests.Ix.Kernel.BuildPrimitives
import Tests.Ix.IxonV4Paths

open Tests.Ix.Kernel.BuildPrimitives

def usage : String :=
  s!"usage: lake exe ixon-v4-primitives

Compile the primitive dependency closure of the installed Lean environment,
write its canonical primitive addresses and the compiled closure to the scratch
directory, and check the addresses against Tests/Fixtures/ixon-v4/primitives.tsv.

{Tests.IxonV4.scratchUsage}"

def main (args : List String) : IO Unit := do
  if args.contains "--help" then
    IO.println usage
    return
  let dir ← Tests.IxonV4.scratchDir
  IO.FS.createDirAll dir
  let tsvPath := Tests.IxonV4.primitivesTsv dir
  let leanEnv ← get_env!
  let needed := collectDeps leanEnv (kernelPrimitives.map parseNameToLean)
  let constants := leanEnv.constants.toList.filter fun (name, _) => needed.contains name
  IO.println s!"Compiling {constants.length} primitive dependency declarations"
  let raw ← Ix.CompileM.rsCompileEnvFFI constants
  let env := raw.toEnv
  let mut text := s!"# Ixon v{Ixon.Env.VERSION} canonical primitive addresses\n"
  for name in kernelPrimitives do
    let some named := env.named[parseIxName name]?
      | throw <| IO.userError s!"missing primitive {name}"
    text := text ++ s!"{name}\t{named.addr}\n"
  IO.FS.writeFile tsvPath text
  let bytes ← match Ixon.serEnv env with
    | .ok bytes => pure bytes
    | .error error => throw <| IO.userError error
  IO.FS.writeBinFile (Tests.IxonV4.primitivesIxe dir) bytes
  IO.println s!"Exported {kernelPrimitives.size} primitive addresses and \
    {env.consts.size} constants to {dir}"
  -- The checked-in table must be this output: it is the record the Rust
  -- `PrimAddrs::new`, `Ix/Tc/Primitive.lean` and the IxVM literals mirror.
  unless (← IO.FS.readFile "Tests/Fixtures/ixon-v4/primitives.tsv") == text do
    throw <| IO.userError s!"Tests/Fixtures/ixon-v4/primitives.tsv differs from the live \
      addresses; copy {tsvPath} over it and update `PrimAddrs::new`"
