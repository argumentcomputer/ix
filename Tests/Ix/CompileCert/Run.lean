import Tests.Ix.CompileCert.Direct
import Tests.Ix.CompileCert.Blocks
import Tests.Ix.CompileCert.Compiled
import Tests.Ix.CompileCert.Stored
import Tests.Ix.CompileCert.Groups
import Tests.Ix.CompileCert.Universes
import Tests.Ix.CompileCert.Expressions
import Tests.Ix.CompileCert.SourceInstall

/-- Standalone remote driver; shared test registration belongs to the
coordinator. Production/test library modules do not define a global main. -/
def main (args : List String) : IO Unit := do
  match args with
  | ["direct"] => Tests.Ix.CompileCert.Direct.run
  | ["blocks"] => Tests.Ix.CompileCert.Blocks.run
  | ["groups"] => Tests.Ix.CompileCert.Groups.run
  | ["universes"] => Tests.Ix.CompileCert.Universes.run
  | ["expressions"] => Tests.Ix.CompileCert.Expressions.run
  | ["source-install"] => Tests.Ix.CompileCert.SourceInstall.run
  | ["compiled"] => Tests.Ix.CompileCert.Compiled.run
  | ["stored", path] => Tests.Ix.CompileCert.Stored.run path
  | [] =>
    Tests.Ix.CompileCert.Direct.run
    Tests.Ix.CompileCert.Blocks.run
    Tests.Ix.CompileCert.Groups.run
    Tests.Ix.CompileCert.Universes.run
    Tests.Ix.CompileCert.Expressions.run
  | _ => throw (IO.userError "expected direct, blocks, compiled, or stored PATH selector")
