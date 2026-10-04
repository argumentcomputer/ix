import Tests.Ix.CompileCert.Direct
import Tests.Ix.CompileCert.Blocks

/-- Standalone remote driver; shared test registration belongs to the
coordinator. Production/test library modules do not define a global main. -/
def main (args : List String) : IO Unit := do
  match args with
  | ["direct"] => Tests.Ix.CompileCert.Direct.run
  | ["blocks"] => Tests.Ix.CompileCert.Blocks.run
  | [] =>
    Tests.Ix.CompileCert.Direct.run
    Tests.Ix.CompileCert.Blocks.run
  | _ => throw (IO.userError "expected optional direct or blocks selector")
