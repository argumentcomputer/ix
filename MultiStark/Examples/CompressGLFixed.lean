import MultiStark.CompressGLFixed

/-! Exports CompressGL for one pinned wrapper key:
`compress_gl_fixed_export WRAP_KEY ARTIFACT [--no-trace]`. -/
def main (args : List String) : IO Unit := do
  let keyPath :: out :: _ := args
    | throw (IO.userError "usage: compress_gl_fixed_export WRAP_KEY ARTIFACT [--no-trace]")
  let bytes ← MultiStark.CompressGLFixed.compilePackage (← IO.FS.readBinFile keyPath)
    (!args.contains "--no-trace")
  Aiur.Artifact.write out bytes
  IO.println s!"CompressGL over BN254, fixed wrapper key: {bytes.size} bytes to {out}"
