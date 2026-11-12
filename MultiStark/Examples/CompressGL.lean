import MultiStark.CompressGL

def main (args : List String) : IO Unit := do
  let path := args.headD "/tmp/ix-compress-gl.ixa"
  let bytes ← MultiStark.CompressGL.compilePackage (!args.contains "--no-trace")
  Aiur.Artifact.write path bytes
  IO.println s!"CompressGL over BN254: {bytes.size} bytes to {path}"
