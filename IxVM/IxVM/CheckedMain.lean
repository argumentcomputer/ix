import IxVM.CheckedGen

/-! `lake exe ixvm/ixvm-checked [--check]`: write the checked IxVM source's
Lean files (`IxVM.CheckedGen.render`), or, with `--check`, compare them with
the files on disk and fail when one differs or is missing, or when a stale
file is left under `IxVM/IxVM/Checked/Fn`. The test suite `ixvm-checked-source`
also checks that the literal is the preparation's value. -/

open IxVM.CheckedGen

def main (args : List String) : IO UInt32 := do
  let check := args.contains "--check"
  let prepared ← IO.ofExcept (Aiur.Modules.prepare IxVM.program [entry])
  let files := render prepared
  let mut ok := true
  for (path, text) in files do
    if check then
      let existing ← try pure (some (← IO.FS.readFile path)) catch _ => pure none
      if existing == some text then
        IO.println s!"[ixvm-checked --check] {path} up to date"
      else
        IO.eprintln s!"[ixvm-checked --check] {path} STALE: run `lake exe ixvm/ixvm-checked` and commit the result"
        ok := false
    else
      let existing ← try pure (some (← IO.FS.readFile path)) catch _ => pure none
      if existing != some text then
        if let some dir := path.parent then IO.FS.createDirAll dir
        IO.FS.writeFile path text
        IO.println s!"[ixvm-checked] wrote {path}"
  let rendered := files.map (·.1.toString)
  let fnDir : System.FilePath := "IxVM/IxVM/Checked/Fn"
  if ← fnDir.pathExists then
    for entry in ← fnDir.readDir do
      let path := (fnDir / entry.fileName).toString
      unless rendered.contains path do
        IO.eprintln s!"[ixvm-checked] {path} is not rendered: remove it"
        ok := false
  return if ok then 0 else 1
