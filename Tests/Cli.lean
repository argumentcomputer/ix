/-! Integration tests for the Ix CLI -/

def Tests.Cli.run (buildCmd: String) (buildArgs : Array String) (buildDir : Option System.FilePath) : IO UInt32 := do
  let proc : IO.Process.SpawnArgs :=
    match buildDir with
    | some bd => { cmd := buildCmd, args := buildArgs, cwd := bd }
    | none => { cmd := buildCmd, args := buildArgs }
  let out ← IO.Process.output proc
  if out.exitCode ≠ 0 then
    IO.eprintln out.stderr
  else
    IO.println out.stdout
  return out.exitCode

def Tests.Cli.suite : IO UInt32 := do
  let _install ← Tests.Cli.run "lake" (#["run", "install"]) none
  let ixTestDir := (← IO.currentDir) / "ix_test"
  let _store ← Tests.Cli.run "ix" (#["store", "IxTest.lean"]) (some ixTestDir)
  let _prove ← Tests.Cli.run "ix" (#["prove", "IxTest.lean", "one"]) (some ixTestDir)
  return 0
