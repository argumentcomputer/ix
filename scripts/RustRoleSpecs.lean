import Ix.RoleBinding.RustSpecGen

def main (args : List String) : IO UInt32 := do
  let source ← IO.ofExcept Ix.RoleBinding.RustSpecGen.render
  let shapePath : System.FilePath := "Tests/Fixtures/role-binding-v2/spec-shape.tsv"
  match args with
  | ["--check"] =>
    unless (← shapePath.pathExists) &&
        (← IO.FS.readFile shapePath) == Ix.RoleBinding.RustSpecGen.shape do
      IO.eprintln s!"{shapePath} is missing or stale; regenerate the role shape fixture"
      return 1
  | ["--out", output] => IO.FS.writeFile output source
  | ["--shape-out", output] => IO.FS.writeFile output Ix.RoleBinding.RustSpecGen.shape
  | [] =>
    IO.FS.writeFile shapePath Ix.RoleBinding.RustSpecGen.shape
  | _ =>
    IO.eprintln "usage: RustRoleSpecs.lean [--check | --out PATH | --shape-out PATH]"
    return 1
  return 0
