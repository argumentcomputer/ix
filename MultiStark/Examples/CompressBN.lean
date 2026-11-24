import MultiStark.BN.Program

open Aiur in
def main (args : List String) : IO Unit := do
  let path := args.headD "target/compress-bn/compress-bn.ixa"
  let entries := if args.contains "--verifier" then [MultiStark.BN.verifierEntry]
    else [MultiStark.BN.compressionEntry]
  let bytes ← MultiStark.BN.compilePackage (!(args.contains "--no-trace")) entries
  Artifact.write path bytes
  IO.println s!"Aiur KZG compression package: {bytes.size} bytes"
