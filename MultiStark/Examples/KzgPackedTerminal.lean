import MultiStark.BN.KzgPackedTerminal

/-! Exports the packed terminal verifier for one fixed predecessor key:
`kzg_packed_terminal_export KEY OUT`. -/
def main (args : List String) : IO Unit := do
  let [key, out] := args | throw (IO.userError "usage: kzg_packed_terminal_export KEY OUT")
  let bytes ← MultiStark.BN.PackedTerminal.compilePackage (← IO.FS.readBinFile key)
  Aiur.Artifact.write out bytes
  IO.println s!"packed terminal artifact: {bytes.size} bytes"
