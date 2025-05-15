/-! Integration tests for the Ix CLI -/

def Tests.ixCli : IO UInt32 := do
  let out ← IO.Process.output { cmd := "lake", args := #["build", "ix"]}
  if out.exitCode ≠ 0 then
    IO.eprintln s!"Build failure exit code: {out.exitCode}\n{out.stderr}"
    return out.exitCode
  return 0
