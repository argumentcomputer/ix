import MultiStark.CompressNarrowFixed

/-! Exports the fixed-key narrow compression stage for one pinned packed
CompressGL key: `compress_narrow_fixed_export GL_KEY ARTIFACT`. -/
def main (args : List String) : IO Unit := do
  let [keyPath, out] := args
    | throw (IO.userError "usage: compress_narrow_fixed_export GL_KEY ARTIFACT")
  let bytes ← MultiStark.NarrowFixed.compilePackage (← IO.FS.readBinFile keyPath)
  Aiur.Artifact.write out bytes
  IO.println s!"Aiur fixed-key narrow stage package: {bytes.size} bytes"
