import Tests.Ix.Kernel.BuildPrimitives
import Tests.Ix.IxonPaths
import Ix.CompileCertified
import Ix.EnvScope

/-!
  Export and verify the Ixon primitive dependency closure and addresses.
-/

open Tests.Ix.Kernel.BuildPrimitives

def usage : String :=
  s!"usage: lake exe ixon-primitives

Compile the primitive dependency closure of the installed Lean environment (its
selected closure, self-contained for the certified checker),
write its canonical primitive addresses and the compiled closure to the scratch
directory, and check the addresses against Tests/Fixtures/ixon/primitives.tsv.

{Tests.IxonPaths.scratchUsage}"

def main (args : List String) : IO Unit := do
  if args.contains "--help" then
    IO.println usage
    return
  let dir ← Tests.IxonPaths.scratchDir
  IO.FS.createDirAll dir
  let tsvPath := Tests.IxonPaths.primitivesTsv dir
  let leanEnv ← get_env!
  -- the selected closure, self-contained for IxC (recursors, literal support):
  -- `ixon-tests --primitives` validates it
  let constants := Ix.EnvScope.collectSelectedDeps leanEnv
    (kernelPrimitives.map parseNameToLean).toList
  IO.println s!"Compiling {constants.length} primitive dependency declarations"
  let out ← IO.ofExcept (← Ix.CompileM.compileCertified leanEnv constants)
  let env := out.env
  let mut text := s!"# {Ixon.wireFormatId} canonical primitive addresses\n"
  for name in kernelPrimitives do
    let some named := env.named[parseIxName name]?
      | throw <| IO.userError s!"missing primitive {name}"
    text := text ++ s!"{name}\t{named.addr}\n"
  IO.FS.writeFile tsvPath text
  let bytes ← match Ixon.serEnv env with
    | .ok bytes => pure bytes
    | .error error => throw <| IO.userError error
  IO.FS.writeBinFile (Tests.IxonPaths.primitivesIxe dir) bytes
  IO.println s!"Exported {kernelPrimitives.size} primitive addresses and \
    {env.consts.size} constants to {dir}"
  -- The checked-in table must be this output: it is the record the Rust
  -- `PrimAddrs::new`, `Ix/PrimAddrs.lean` and the IxVM literals mirror.
  unless (← IO.FS.readFile "Tests/Fixtures/ixon/primitives.tsv") == text do
    throw <| IO.userError s!"Tests/Fixtures/ixon/primitives.tsv differs from the live \
      addresses; copy {tsvPath} over it and update `PrimAddrs::new`"
